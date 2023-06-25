import type { StoryObj } from '@storybook/react';
import List from "../components/List";
declare const meta: {
    title: string;
    component: typeof List;
    tags: string[];
};
export default meta;
type Story = StoryObj<typeof List>;
export declare const Primary: Story;
