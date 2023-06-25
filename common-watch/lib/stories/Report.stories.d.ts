import type { StoryObj } from '@storybook/react';
import Report from "../components/Report";
declare const meta: {
    title: string;
    component: typeof Report;
    tags: string[];
};
export default meta;
type Story = StoryObj<typeof Report>;
export declare const Primary: Story;
