import type { StoryObj } from '@storybook/react';
import Application from "../components/Application";
declare const meta: {
    title: string;
    component: typeof Application;
    tags: string[];
};
export default meta;
type Story = StoryObj<typeof meta>;
export declare const Primary: Story;
